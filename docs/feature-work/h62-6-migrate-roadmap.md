# H62 item 6: migrate-roadmap

Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-roadmap`.
Repository: `/workspace/solidity-lean`.
This is an isolated migration overlay; live producer ownership is unchanged.
No production Lean file, toolchain pin, generated root or central map is edited.

## Status and reproducibility

All four checkpoints remain incomplete. The source census covers 15 assigned
modules, 374 local closure modules, and 20 direct cross-directory import edges.
Its 415 lexical declaration commands are navigation records, not an elaborated
API inventory. Whole-source SHA256 freezes all bodies, types and options; this
alone does not establish semantic compatibility under a different Lean version.
No theorem statement, premise, proof budget or representation has changed.
No declarations/helpers were added to production Lean; no new axiom or sorry.
Additive test helpers contain four fixture theorems and two read-only API exporters.

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
fragments.sh --check both exited 0. Full old build, elaborated interface census,
new assigned-module acceptance, successful timing delta, final runtime gate,
final milestone reviews and complete migration bundle remain outstanding.
No owner relay tool exists in this VM checkout; no existing producer file edits
are authorized by an absent reply. Coordinator can retrieve this saved request.

## Compatibility matrix and backfill

The bounded v4.35.0 matrix completed with exit 1, guard=null, 104.440 s,
cgroup peak 447696896 bytes, all inputs unchanged. Evidence:
`/workspace/migrate-roadmap-evidence/h62-roadmap-new-matrix-1793972220053491695/`.
It accounts for all 374 local closure modules: 25 pass, 3 fail and 346 blocked
by known failed prerequisites. Of the 15 assigned modules, Evm passes and 14
are blocked. Ten assigned modules reach Hash; the other branches expose the
additional failures below. A blocked status is not a compilation pass.

Additional typed external blockers, for migration-root/gate owner routing:

- B-DEPENDENCY-SYNTAX: `Solidity/Syntax/Raw.lean`: line 597 String argument
  mismatch, line 650 missing `String.Slice.toList`, line 665 argument mismatch,
  line 684 missing `String.dropRight`, line 682 argument mismatch. READ ONLY.
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

The clean old baseline is still pending: a 723.428 s attempt stopped on a captured
RSS=0 `Zl` Lean row; a subsequent 533.262 s attempt stopped when a first-observed
worker exited before `/proc/PID/exe` could be read. Neither run is valid timing
acceptance. No unknown terminal row was accepted. A final higher-frequency
strict-observer retry is planned before declaring the baseline unavailable.
The v4.35.0 matrix is failure evidence, not an after-build timing for comparison;
timing delta remains unavailable. No slowdown acceptance or RUNTIME_GATE_PASS.
