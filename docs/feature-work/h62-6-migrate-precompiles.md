# H62/H63 Precompiles migration — blocked checkpoint handoff

Batch `solidity-h62-6-20261106`, lane `migrate-precompiles`.
Repository `/workspace/solidity-lean`; isolated branch
`codex/solidity-h62-6-20261106/migrate-precompiles`.
Pinned base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
No push, merge, PR, producer transfer, toolchain cut-over, generated-root change,
axiom-pin edit or freeze announcement occurred. The persistent goal is unfinished.

## Checkpoint status

1. **Census and old clean baseline: done.** Eleven assigned source files,
   237 declaration lines, 152 `#guard` commands and three `#guard_msgs` assertions.
   All original source bytes, tables, statements, definitions and budgets are
   unchanged. Frozen-source SHA256 values are in the lane tests directory.
2. **Pinned new toolchain and migration: blocked.** Official toolchain installed
   and hash-verified; three proof-only candidate edits validated in isolation.
   Producer originals remain read only pending exact-file owner clearance.
   Further axiom-preserving repairs and a root-owner dependency remain.
3. **New build and comparison: blocked.** Candidate v2 compiles the first ten
   assigned modules but Osaka fails its original axiom assertions. A failed
   build is not eligible for the final wall-time comparison.
4. **Final root-gate handoff: partial.** Census, tooling, fixtures, owner requests,
   candidate patch fragments and evidence are reviewable. Final migrated source,
   passing full gates, final timing comparison and acceptance are outstanding.

## Setup and exact toolchain

Initial checkout was clean branch `work`, head
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4`. Fetched published master and the exact
base, verified `git merge-base --is-ancestor BASE origin/master` (exit 0), then
created the assigned branch directly at BASE. No reset or discarded work.
Published master observed during setup was `821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`.
AGENTS, intrinsic Gate G0, module map, producer history, parallelism, contribution
and resource instructions were inspected. No Lean MCP or coordinator `relay.sh`
is exposed here; per-file command-line diagnostics are used instead. The supplied
continuation objective is preserved; no second goal was created.

Coordinator inputs `/workspace/h62-coordinator-inputs/sha256.json` verify all five
provided documents. The shared `toolchain-pin.json` specifies
`leanprover/lean4:v4.35.0`, official `lean-4.35.0-linux.tar.zst`:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The downloaded archive matches exactly, rather than using an independently built
compiler. Private toolchain path:
`/workspace/h62-migrate-precompiles/toolchains/lean-4.35.0-linux`.
Tracked `lean-toolchain` remains `leanprover/lean4:v4.24.0`.

Actual versions:

- Lean 4.24.0, x86_64-unknown-linux-gnu, release commit
  `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
  Lake `5.0.0-src+797c613` (Lean 4.24.0).
- Lean 4.35.0, x86_64-unknown-linux-gnu, release commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Lake `5.0.0-src+eb6cafb` (Lean 4.35.0).

## Resources, commands and decisive evidence

VM cgroup memory cap 16 GiB, CPU quota 4 cores across allowed CPUs 0–4,
no system swap; no systemd-run used. Each Lean child
has a hard 12 GiB address-space limit, one thread, explicit `-j1`,
`--tstack=131072`, and a guard retaining at least 4 GiB of physical/cgroup
headroom. A shared writer lock is acquired and inherited by the child; abnormal
Python exit kills/reaps its owned child where possible, and parent death cannot
release the inherited lock while the child survives. No other workers were killed.
Heavy checks were serial. Per-child RSS comes from `wait4`, not cumulative rusage.
Clean means an absent private output directory and empty olean product directory;
no Lake/master artifact cache is used. OS page cache was not explicitly flushed.

All paths below are relative to
`/workspace/h62-migrate-precompiles/evidence/` unless stated otherwise.
The full underlying Lean commands, exits, per-module wall/RSS, expected/completed
inventory and compiler versions are in each `summary.json`.
The common runner is
`scripts/h62/item6/migrate-precompiles/bounded-build.py`.

| Gate / command arguments | Outcome | Decisive evidence |
|---|---|---|
| `census.py --verify` | pass | `census.json`: all 11 sources equal base |
| `acceptance.py` | pass | `acceptance-final.log`: 11 source mutations, inventory/cycle controls, attribute/guard coverage, partial/failure/no-output/cache controls, parent-death lock control |
| runner `--keysort-only --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out .../old-keysort-final` | pass | Exactly `Solidity.KeySort`, 1/1, exit 0, 2.316 s, 264332 KiB |
| runner `--keysort-only --toolchain .../lean-4.35.0-linux --out .../new-keysort-final` | pass | Exactly `Solidity.KeySort`, 1/1, exit 0, 1.818 s, 512164 KiB |
| runner `--toolchain /workspace/.setup/tools/lean-4.24.0-linux --out .../old-measured` | pass | 16/16; 46.390716473 s; max worker RSS 375120 KiB |
| runner new toolchain, `--out .../new-measured` | fail | BLS discount length `rfl` exceeds recursion depth, lines 171/172 |
| runner from private `candidate-sources`, new toolchain | fail | BLS fixed; PointEval line 141 `Option.noConfusion` universe mismatch |
| runner from private `candidate-v2-sources`, new toolchain | fail | 16 attempted, 15 pass; Osaka axiom assertions fail, lines 198/202 |
| diagnostic `Inspect.lean`, old/new matching `--import-products` | pass | 221 named declarations each; `interface-comparison.json`: zero formatted signature changes, 69 axiom-set changes |
| `DiscountKernel`, `BindCheck`, `StipendProof`, `FinEquality` fixtures on each toolchain | pass | Each fixture's old/new summary and log; exact statements, no budget overrides |
| final clean migrated build / final timing / `./run-lean.sh` | pending | Cannot pass before owner/dependency repairs and original axiom assertions pass |

Diagnostic import reuse is explicitly labeled in summaries and never counted as a
clean timing. Two early pilot closure builds (`old-keysort`, `old-clean`) are
excluded: the first was mislabeled because the caller omitted `--keysort-only`.
`old-keysort-actual` is an incomplete pilot from discovering missing `/usr/bin/time`;
final measurements instead use per-process `wait4`. A double-lock invocation was
rejected and did not run Lean. Failed plain-decide and simp alternatives remain
only as off-git pilot evidence, not accepted proofs or production changes.

The failed candidate-v2 wall time is 34.648226113 s with peak 599552 KiB.
**No final speedup percentage is claimed from a failed build.** The observed peak
RSS increase versus the old full run is 59.83%; this is explicitly escalated to
migration root/gate, not accepted as a passing resource comparison. No final
slowdown gate has passed; >10% checking slowdown must stop the migration.

## Exact candidate and blockers

`proposed-bls.patch` replaces only the two length theorem bodies `rfl` with
`by decide +kernel`. Both tables still contain the same 128 entries, both
statements are identical, and both version fixture logs report no axioms.
The official tactic's kernel path constructs and kernel-checks a proof; it does
not use native evaluation or a trusted Bool-reduction axiom. No heartbeat or
recursion-depth setting is raised. A rejected simplifier alternative added
`propext`, so it was not selected.

`proposed-pointeval.patch` replaces only the impossible `none` branch
`exact Option.noConfusion h` with `cases h`. The exact polymorphic statement
passes both versions; its fixture uses only `propext`, as the original helper.
No decoding/verifying irreducibility or definition was changed.

`candidate.py --out NEW_DIRECTORY` deterministically copies the 16-source closure
and applies only these three proof edits to an **off-git** snapshot. Its `.git`
symlink is used only for `git show BASE:path`; it is not a standalone checkout and
must never be used for Git mutations or included as an independent repository.
Snapshots and artifacts are private diagnostics, not approved producer edits.

Typed pending requests are recorded in `owner-requests.json`:

- `OWNER-BLS`, `OWNER-POINT`: exact-file clearance requested in this thread via
  Q-OWNER-BLS-01 / Q-OWNER-POINT-01; no answer grants permission by silence.
- `ROOT-AXIOMS`: migrate-root-gate owns `Solidity/Secp256k1.lean`, which must retain
  the approved `recover` API and frozen axiom expectations. Under the new inferred
  standard instances, `Precompiles.ecrecover` changes from `[propext]` to
  `[propext, Classical.choice, Quot.sound]`. This lane will not edit that file.
- `LOCAL-AXIOMS`: producer clearance needed for subsequent exact-preserving Field
  and Osaka repairs. The new `finFieldOps` print shows inherited BEq going through
  `Std.PreorderPackage.toBEq` and `Fin.instLinearOrderPackage`; the individual
  `Fin.ofNat/add/sub/mul/neg` and `Nat.mod_lt` remain axiom-free. The diagnostic
  `upstream-new` has one expected unknown-name lookup (`Fin.instBEq`) and is not a
  passing gate. Do not repin the failed Osaka expectations.
- `RSS-REGRESSION`: higher RSS escalated above. `FULL-GATE`: all remaining final
  validation, accepted timing, finder/skeptic review and final migration handoff.

Direct outside-directory imports are `Solidity.Roadmap.Evm`, `Solidity.Hashes`,
`Solidity.Secp256k1`; closure adds `Solidity.Keccak`, `Solidity.RevertBytes`.
All five compile unchanged on the new version, but compiling is not evidence that
their transitive axiom dependencies are unchanged. Roadmap owner retains Evm;
root migration owner retains the other four. No source request was sent using an
unavailable relay; the coordinator retrieves this saved exact-file report.

## Backfill, proof boundaries and review

`FinEquality` proves, for every modulus and pair of finite values, that explicit
`Nat.beq` of their values agrees with the current lawful comparison. The explicit
computational definition is axiom-free on both versions; its agreement proof has
standard axioms (new version includes Classical.choice) and is not smuggled into
a frozen theorem. `StipendProof` uses explicit `Nat.decLt` to prove the exact
numeric stipend obligation with no axioms on either version. These fixtures do
not by themselves repair the frozen public Osaka theorem.

There are no source `sorry`, new `axiom`, `native_decide`, kernel-skip options,
raised proof budgets or weakened statements/premises/exclusions in this change.
Rejected failed elaborations may print `sorryAx`; no such artifact is accepted.
The 152 original computation guards are preserved. They are finite executable
vectors, not proofs of elliptic-curve/field laws or external-EVM equivalence.
The named signature comparison hashes normalized printed types, not kernel Expr
objects; complete original source hashes cover all declaration/case bytes,
including anonymous instances. Osaka's 11 source declarations remain frozen but
its new-toolchain axiom gate fails, so full elaborated interface acceptance is
not claimed. There are no new area modules to register; helpers remain in tests.

Independent read-only finder and skeptic reviewed census/runner, identified and
closed missing attributed declarations, missing guard_msgs, premature PASS,
cumulative RSS and child cleanup/lock issues. Acceptance controls cover them.
Both separately verified the two length proof candidates' exact tables,
statements and empty axiom sets, and the off-git snapshot's exact three-proof
scope was presented for further review. Neither reviewer ran Lean or a server.
Final milestone reviews are recorded in the off-git review evidence after review
of this document; no review substitutes for the failing required gates.

Resume on this VM/goal/branch. Obtain exact-file owner clearances and the root
axiom-preserving dependency first. Never infer approval to modify pins. Re-run
clean old/new comparable measurements after implementing authorized repairs,
stop/escalate regressions, run the required full affected/final gates, obtain
fresh independent reviews, and export the final complete patch/bundle. Keep the
same persistent goal unfinished; coordinator owns any fresh-thread handoff.

Final independent finder and skeptic reviews found no serious defect in this
blocked handoff and verified the production sources remain byte-identical.
Their review approves reporting accuracy, not failed migration gates.
`compare-inspection.py` exit 0 establishes signatures only; its 69 axiom deltas
remain blockers. Repository static checks pass: layers (857 core modules),
generated roots, generated fragments, and documentation paths. Their commands
and outputs are in `static-gates.json` and the corresponding evidence logs.
