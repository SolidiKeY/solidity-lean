# H62 item 6: migrate-roadmap

Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-roadmap`.
Repository: `/workspace/solidity-lean`.
This is an isolated migration overlay; live producer ownership is unchanged.
No production Lean file, toolchain pin, generated root or central map is edited.

## Status and reproducibility

Checkpoint 1 (pinned-base census and clean old build) is complete.
Checkpoint 2 is partial; checkpoints 3 and 4 remain blocked/partial as described below. The source census covers 15 assigned
modules, 374 local closure modules, and 20 direct cross-directory import edges.
Its 415 lexical declaration commands are navigation records, not an elaborated
API inventory. Whole-source SHA256 freezes all bodies, types and options; this
alone does not establish semantic compatibility under a different Lean version.
No theorem statement, premise, proof budget or representation has changed.
No declarations/helpers were added to production Lean; no new axiom or sorry.
Additive test helpers contain six test theorems, two candidate compatibility abbreviations, and two API exporters.

Run `python3 scripts/h62/item6/migrate-roadmap/census.py` to regenerate the
census. Run `python3 tests/h62/item6/migrate-roadmap/test_census.py` for scanner
negative controls and full-closure topological/determinism checks.
Use `python3 scripts/h62/item6/migrate-roadmap/build.py old|new prerequisite|baseline|after|fixtures|matrix|api [successful-result.json]`
for clean, cache-disabled, serial module builds. Each invocation creates a new
off-git output directory under `/workspace/migrate-roadmap-evidence` and retains
command, versions, logs, exact input hashes, wall time, sampled aggregate RSS,
11 GiB cgroup cap, no-swap check, one CPU, 4 GiB reserve guard and a 300 s per-module
wall limit. Builds use the repository's import-closure approach, not the final
`./run-lean.sh` gate; that full gate remains pending. Failed or guard-stopped
runs cannot be used for before/after performance acceptance.

The official v4.35.0 archive is `/workspace/migrate-roadmap-toolchains/lean-4.35.0-linux.tar.zst`,
SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`, matching
`/workspace/h62-coordinator-inputs/toolchain-pin.json`. All five coordinator
input manifest checks passed. Actual versions: Lean 4.24.0 commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake 5.0.0-src+797c613;
Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake 5.0.0-src+eb6cafb.
Both bounded KeySort prerequisites have passed; no RUNTIME_GATE_PASS is claimed.
No v4.24 per-master artifact cache is used.

## Typed blocker B-DEPENDENCY-HASH

Consumer: `Solidity/Roadmap/Contracts.lean`.
External dependency: `Solidity/Hash/CollisionBound.lean` (READ ONLY here).
Recipient: migration root/gate for routing to the Hash migration owner.
Exact v4.35.0 probe failed at lines 407, 660 and 680 (unsolved function equality
and omega goals), followed by recovery `sorryAx` axiom-message mismatches.
Reproduction: `python3 scripts/h62/item6/migrate-roadmap/build.py new baseline`.
Evidence: `/workspace/migrate-roadmap-evidence/h62-roadmap-new-baseline-1793970405860872982/`.
The bounded run exited 1, guard=null, wall 5.436 s, cgroup peak 206467072 bytes.
These are failed-probe measurements, not a clean successful build baseline.
Request: supply owner-reviewed exact-semantics v4.35.0 dependency migration,
without weakening statements, adding axioms or increasing proof budgets.
No outside-scope patch or dependency cache has been substituted.

## Independent read-only reviews

Finder and skeptic independently reviewed the census and runner without Lean
servers or builds. Both found Docker top required PID, leaving the first
observer fail-open, and required full-closure/config fingerprints. Fixed both:
PID-aware observation fails closed; old inputs must match the pinned base;
all closure/config inputs are hashed before/after; tooling/config hashes saved.
Both re-reviewed and confirmed these fixes. The passing old prerequisite
`1793970040113808306` predates expanded fingerprint metadata, so it proves only
KeySort compilation/observation, not the later input-fingerprint claims.

Discarded runs remain off git: initial missing-image argument (exit 125),
zero-observation prerequisite (invalid RSS evidence), manually stopped old run
(exit 137), strict serial-guard-stopped old run (195.094 s, no rejected snapshot),
and new metadata invocation `lean --version` rejected without `-j1` (captured).
Version reporting now explicitly uses `lean -j1 --version`. The strict live-worker guard
remains unchanged. The unchanged repository pidfd tracker now normalizes only
previously identity-bound processes with kernel-confirmed termination; executable
inodes must match the selected official binary. Unknown or unbound terminal rows
still reject. Its 43 negative/identity controls passed. Observation sleep is now
0.02 s rather than 0.5 s, to bind short-lived workers sooner; this changes no
proof, time, memory or acceptance budget. The earlier
195 s guard stop is unexplained and must not count as a valid baseline.

Structural read-only checks passed: check-layers reports 857 core modules with
zero elaborator/parser-adapter reachability; register.sh --check and
fragments.sh --check both exited 0. New assigned-module acceptance, successful timing delta, final runtime gate,
full migration acceptance remains outstanding. Final evidence reviews are recorded below.
No owner relay tool exists in this VM checkout; no existing producer file edits
are authorized by an absent reply. Coordinator can retrieve this saved request.

## Compatibility matrix and backfill

The bounded v4.35.0 matrix completed with exit 1, guard=null, 104.440 s,
cgroup peak 447696896 bytes, all inputs unchanged. Evidence:
`/workspace/migrate-roadmap-evidence/h62-roadmap-new-matrix-1793972220053491695/`.
It accounts for all 374 local closure modules: 24 pass, 4 fail and 346 blocked
by known failed prerequisites. Of the 15 assigned modules, Evm passes and 14
are blocked. Ten assigned modules reach Hash; the other branches expose the
additional failures below. A blocked status is not a compilation pass.

Additional typed external blockers, for migration-root/gate owner routing:

- B-DEPENDENCY-SYNTAX: `Solidity/Syntax/Raw.lean`: line 597 String argument
  mismatch, line 650 missing `String.Slice.toList`, line 665 argument mismatch,
  line 684 missing `String.dropRight`, line 682 argument mismatch. READ ONLY.
- B-DEPENDENCY-SOURCE: `Solidity/Source/Ctor.lean:641`: default 200000-heartbeat
  simp failure; line 715 dependent elimination failures. READ ONLY. No budget
  increase is proposed or authorized.
- B-DEPENDENCY-CREATION: `Solidity/Backend/Creation/Linking.lean:109`: type
  mismatch after simplification. READ ONLY. Exact diagnostics in matrix log.

No owner fixes were attempted. The matrix awaits each Lake module invocation
and invokes it only after every local imported module has passed, preventing
retry-driven concurrent dependency builds. Per-module pass/fail/blocked stamps
and complete status metadata are retained. The generated shell is stored and
syntax-checked, avoiding OS argument-size limits. Earlier stopped/failed harness
attempts are retained and excluded from performance acceptance.

The independent new-toolchain backfill run
`/workspace/migrate-roadmap-evidence/h62-roadmap-new-fixtures-1793971395782971642/`
passed, exit 0, guard=null, 21.857 s. It compiles the original Evm module,
proves the exact Nat equality/countP split left at Hash line 407, and proves
negative controls rejecting a dropped head and dropped tail. The fixture uses
only standard axioms `[propext, Quot.sound]`; it does not discharge either
arithmetic blocker. The Evm exporter accounts for 391 elaborated constants,
including generated/private constants. `type_debug` is a version-specific
fingerprint, not cross-version type-equality proof; `theorem_axioms` is collected
only for theorem constants, not a complete trust inventory.

Finder and skeptic independently reviewed the pidfd adaptation, official-binary
inode check, fixtures and API exporters without Lean/builds. Neither found a
blocking flaw. Their documentation findings (terminal normalization wording,
limited axiom inventory, and revision of byte-identical controls if authorized
proof bodies later change) are retained here. Existing production source
hashes remain exactly the pinned base, including all frozen statements.

Discarded clean-old attempts: a 723.428 s attempt stopped on a captured
RSS=0 `Zl` Lean row; a subsequent 533.262 s attempt stopped when a first-observed
worker exited before `/proc/PID/exe` could be read. Neither run is valid timing
acceptance. No unknown terminal row was accepted. The final higher-frequency
strict-observer retry passed; its results follow.
The v4.35.0 matrix is failure evidence, not an after-build timing for comparison;
timing delta remains unavailable. No slowdown acceptance or RUNTIME_GATE_PASS.

## Successful pinned-base census milestone

Command: `python3 scripts/h62/item6/migrate-roadmap/build.py old baseline`.
Evidence: `/workspace/migrate-roadmap-evidence/h62-roadmap-old-baseline-1793972395093467937/`.
Exit 0, guard=null: all 374 closure modules and all 15 assigned modules pass.
Clean build wall: **1777.474265893 s**. Sampled aggregate peak RSS:
**1704960000 bytes**; exact cgroup peak: **2156396544 bytes**. There were 38458
observations. All source/config fingerprints before/after match. The measured
build used committed head `3bd09fb8d6b66103b03a1efed46fc6dc01acfc53` with every
production input exactly pinned base; later changes are documentation/tooling.
Private build output was initially absent; artifact cache disabled. OS page
cache was not forcibly flushed. Earlier failed attempts do not enter this number.

Command: `python3 scripts/h62/item6/migrate-roadmap/build.py old api /workspace/migrate-roadmap-evidence/h62-roadmap-old-baseline-1793972395093467937/result.json`.
Evidence: `/workspace/migrate-roadmap-evidence/h62-roadmap-old-api-1793974186713389076/`.
Exit 0, guard=null. **2077 elaborated declarations across all 15 modules**,
including generated/private declarations, are accounted for. This export reused
only the verified successful old build and took 35.219 s, excluded from build wall.
The complete old declaration inventory and partial new Evm inventory are stored
off git, with per-module source and debug-type fingerprints; all source hashes
remain byte-identical to base. These are not cross-version semantic equality proofs.

The deterministic off-git data generator is
`scripts/h62/item6/migrate-roadmap/evidence.py`; pass the old build, complete new
matrix, old API and new fixture `result.json` paths. It checks all matrix
prerequisite/status relationships, source stability, exact declaration coverage
and theorem-only standard axiom sets before emitting the census, API data,
frozen-interface hashes, four typed owner requests and validation summary.

Correction retained for review: the initial checkpoint manually reported 25/3;
the complete status metadata and independent reviews establish **24 pass / 4 fail**.
Both reviewers independently verified the corrected complete matrix and all four
external diagnostics. All 374 matrix source hashes match the pinned base.

No successful new full closure exists, so no after-build time or slowdown delta
is available. No performance acceptance or final runtime gate is claimed. Four
external owner repairs are necessary; downstream incompatibilities may remain.
No new production registration is needed: test helpers stay unregistered under
the assigned tests directory. Final `lean-toolchain` cut-over remains the root lane.

## API preservation blocker and tested proposal

The final finder review compared names as well as counts: old Evm has 392
elaborated constants, new Evm 391, with **three removed and two added names**.
Removed: `Solidity.Roadmap.Evm.Fork.toCtorIdx`,
`Solidity.Roadmap.Evm.Precompile.toCtorIdx`, and
`Solidity.Roadmap.Evm.beBytes._proof_2`. Added:
`Solidity.Roadmap.Evm.rlpBytes._sparseCasesOn_1` and `_2`.
All removals and common debug-type changes are retained in
`/workspace/migrate-roadmap-evidence/api-compatibility-deltas.json`.
No compiler-generated declaration is silently dropped from accounting.
An Evm compilation pass does **not** establish frozen API preservation.

B-OWNED-EVM-API is an exact-file coordination request to migration-root/gate
and the live Evm producer for `Solidity/Roadmap/Evm.lean`. The unapplied,
reviewable proposal is `/workspace/migrate-roadmap-evidence/evm-compatibility-proposal.patch`.
It restores both legacy enum abbreviations and the exact termination-proof
proposition. The abbreviations preserve the old compiler's reducible/protected
status and deprecation target/date (`2025-08-25`), verified from official old
`Lean/Meta/Constructions/CtorIdx.lean`. No existing Evm file has been edited;
absence of an owner reply is not permission to apply this proposal.

The proposal's exact declarations are tested only in the additive fixture.
Final new fixture evidence:
`/workspace/migrate-roadmap-evidence/h62-roadmap-new-fixtures-1793974979117587979/`:
exit 0, guard=null, 20.759 s. All original Hash subgoal/negative controls still
pass, along with restored API types, the termination proposition, the universal
Fork index theorem and all 19 enum-value guards. The termination proof uses
only `propext`; the Fork index theorem uses no axioms. No new axiom/sorry/native
shortcut or raised budget exists. Production API restoration remains blocked.

Final old API/enum evidence:
`/workspace/migrate-roadmap-evidence/h62-roadmap-old-api-1793975052419846724/`:
exit 0, guard=null, 32.575 s, 2077 original declarations and all 19 matching
legacy enum guards. This refresh is separate from the 1777.474 s clean build.
The earlier 35.219 s export remains valid historical inventory evidence but
final data regeneration uses the refreshed matching helper-source fingerprints.

The generator now enforces current compiler-source equality, cross-run shared compiler-input
identity, and equal recorded resources in all four selected runs, addressing
the final skeptic finding. Source hashes for all 15 production modules remain
exactly the pinned base. API fingerprints include original and new generated
names; they are not a cross-version equality proof or complete trust audit.

Some later short fixture refreshes were conservatively rejected at container
startup and are excluded. The runner now has a startup barrier: actual memory
and swap limits are checked before readiness, no Lean is released until a
successful empty-worker process observation, and a 15 s admission deadline
applies in every pre-admission state. Post-admission observation failures still
reject. The complete historical old build and matrix used identical driver
hashes at `3bd09fb8d6b66103b03a1efed46fc6dc01acfc53`. Any future accepted
before/after pair must use the same chosen driver/settings; remeasure both
sides if changing the measurement driver. No after time is available here.

Final local checks pass: ten census/import/exporter/control-timeout controls,
43 existing fail-closed terminal identity controls, structural layer checks
(857 core modules, no forbidden reachability), generated-root/fragment checks,
and whitespace validation. No full runtime or complete migration acceptance.

Historical matrix/API metadata captured all test helpers even when the shell
never executed them. The generator validates the saved workload script SHA256,
tracks its exact executed helper inputs, and records unused helper captures in
the validation summary. All production source/config inputs remain checked
against current files and across runs. The final runner captures only helpers
actually invoked by its selected mode. Original capture metadata is retained.

Final review clarifications: the helper has six named theorems (four original
Hash/negative controls plus the termination and universal Fork-index theorems),
two compatibility abbreviations, and 19 enum-value guards. There are **64 shared
Evm debug-type signature changes** in addition to the three removed/two added
names. Some include changed generated recursor signatures. All 64 require root
compatibility review under the unchanged frozen-interface obligations; this
lane grants no blanket acceptance or API exception.

Docker observer `top`, `inspect` and `kill` calls now have bounded control-call
timeouts (2 s maximum); a timeout becomes a failed observation. Startup admission
checks its 15 s budget before release as well as between control calls; cleanup
is separately bounded. Post-admission unobservable/live mismatches still reject.
A client that stalls during cleanup yields an explicit unconfirmed-termination
blocker and no successful gate. Two negative controls verify timeout/error
propagation. This fixes the final skeptic's daemon-hang finding; historical
successful evidence is unaffected.

## Final review and retrieval

Finder and skeptic re-reviewed their final findings after fixes, read-only with
no Lean server/builds. Both confirm corrected six-theorem/two-alias accounting,
explicit pending review of 64 changed signatures and no API exception. Skeptic
confirmed bounded Docker control/cleanup and timeout controls; finder confirmed
the tested compatibility proposal and old compiler metadata. No critical finding
remains in this tooling checkpoint. Final pinned-new KeySort prerequisite:
`/workspace/migrate-roadmap-evidence/h62-roadmap-new-prerequisite-1793975540555455971/`,
exit 0, guard=null, successful admission, 38 observations, 2.381 s.

Committed-source patch and bundle will be sealed at
`/workspace/migrate-roadmap-evidence/original.patch` and
`/workspace/migrate-roadmap-evidence/migrate-roadmap.bundle`.
The absolute-path handoff is `/workspace/migrate-roadmap-evidence/HANDOFF.json`;
checksums are `/workspace/migrate-roadmap-evidence/SHA256SUMS`.
The unapplied Evm proposal is separate and requires its exact-file owner reply.
Full committed head/base, result paths, proof boundaries, remaining gates and
original VM/goal context are in the handoff. No push, merge, PR, generated-root,
central-map, axiom-pin or tracked toolchain edit has occurred. The original goal
must remain unfinished and blocked pending the listed owner/API obligations.
