# H62 item 6: migrate-semantics

Status: blocked; no migration acceptance or RUNTIME_GATE_PASS.

Repository: `/workspace/solidity-lean`. Branch:
`codex/solidity-h62-6-20261106/migrate-semantics`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Fetched origin master and the exact base; verified base is its ancestor before
creating the branch. The initially clean `work` branch was preserved. No push,
merge, PR, freeze, generated root, central map, axiom pin, or toolchain edit.
No producer-owned source was edited. No semantic refactor was attempted.

## Checkpoints and blockers

1. Partial: deterministic census covers 82 scoped files, source hashes, lexical
   declarations, imports, reverse consumers (including root modules), and the
   162-module closure with dependency source hashes. Lexical declaration entries
   are not fully qualified API signatures or constructor/field enumeration.
   Clean old diagnostic passed 111 modules then stopped in out-of-scope
   `Solidity.Source.Horizon`: 300.188759636 seconds, exit -9,
   `MODULE_300S_STOP`. Total interrupted run: 989.583601066 seconds;
   cumulative peak child RSS: 3728392 KiB. These are interrupted-run measurements,
   not a complete clean baseline. `BASELINE_INCOMPLETE` remains open.
2. Partial: all coordinator input hashes verified against sha256.json. Official
   archive SHA256 is
   `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
   New Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release;
   Lake: 5.0.0-src+eb6cafb. Old Lean: 4.24.0, commit
   797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release;
   Lake: 5.0.0-src+797c613. New KeySort and AbiEntry pass; AbiAccess fails.
   `OWNER_ACK_REQUIRED`: exact requested file `Solidity/Semantics/AbiAccess.lean`,
   beginning at line 203 and further Except.noConfusion uses. Proposed action:
   replace obsolete constructor-discrimination proof applications with kernel
   case analysis, preserving every declaration signature and proof budget.
   Four isolated constructor fixtures establish that this pattern works on both
   versions; they do not establish that the production repairs work. No relay.sh
   exists in this checkout; owner acknowledgement has not been received. This
   saved request is for coordinator relay, not evidence of permission.
3. Blocked: new diagnostic stops at AbiAccess exit 1. Full assigned build,
   clean matched timing comparison, affected validation and run-lean.sh pending.
   Timing delta is unknown. Existing runs differ in module order and are both
   incomplete. Neither a regression nor compliance with the 10% limit is proved.
4. Partial: source-freeze hashes and cross-directory dependency report are in
   the off-Git census; reviewable tooling patch/bundle and checksums exported.
   No delivery to migrate-root-gate or elaborated frozen-interface hash gate is
   claimed. Root toolchain cut-over remains its owner's work.

## Reproduction and evidence

Bulk evidence: `/workspace/h62-migrate-semantics-evidence/` (off Git).
Coordinator inputs: `/workspace/h62-coordinator-inputs/`.
`census.json` and each diagnostic run's census.json record exact source inputs.
`old-clean-01` is an invalid tooling attempt (missing GNU time); do not use it.

Commands (from repository root):

```sh
python3 scripts/h62/item6/migrate-semantics/census.py --out /workspace/h62-migrate-semantics-evidence/census.json
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/h62-migrate-semantics-evidence/old-clean-02
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --out /workspace/h62-migrate-semantics-evidence/new-clean-01
python3 tests/h62/item6/migrate-semantics/scanner_controls.py
node scripts/check-layers.mjs
git diff --exit-code c6f550e281a7e5affa9a99bc2cdaed556dec00e4 -- Solidity lean-toolchain lakefile.toml
```

Census: exit 0. Old measurement: exit 1 (timeout, not theorem failure).
New measurement: exit 1 (AbiAccess type errors). Each summary.json contains
commands, actual toolchain versions, exits, wall and cumulative peak RSS;
each module has its full diagnostic log. New KeySort log is empty with exit 0
in summary.json. Five scanner negative controls pass. Layer check exit 0:
857 core modules, zero reach elaborator or checked parser adapters. Frozen
source diff exit 0. Both fixture commands exit 0 (`fixture-result.txt`):

```sh
LEAN_NUM_THREADS=1 /workspace/.setup/tools/lean-4.24.0-linux/bin/lean -j1 --tstack=131072 tests/h62/item6/migrate-semantics/ExceptCompatibility.lean
LEAN_NUM_THREADS=1 /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux/bin/lean -j1 --tstack=131072 tests/h62/item6/migrate-semantics/ExceptCompatibility.lean
```

Heavy runs serial, writer-lock protected, explicit -j1 and one Lean thread,
12 GiB address-space cap, 4 GiB headroom guard, no systemd-run. VM cgroup cap
16 GiB; host swap unavailable. No per-master cache used; outputs initially
absent. These direct Lean closure diagnostics do not replace repository final
run-lean.sh, SolKey conformance, or affected validation. No Lean MCP exposed.

## Reviews and backfill

Independent read-only finder and skeptic used neither Lean server nor builds.
Finder: corrected missing GNU time dependency, omitted root consumers, string
comment parsing/false imports, swap prerequisite, and process-exit race.
Skeptic: corrected same-line attributes, staged/untracked source cleanliness,
closure hashes and typed resource-stop recording. A final try/finally cleanup
was added after review to kill/wait owned process groups on interruption;
Python AST syntax checks pass. No production proof fixes were made.
Both reviews reject API-equivalence, full-baseline, performance and acceptance
claims from these results. Final evidence confirms the two partial runs and
limited scope of the four passing fixture examples. Generated __pycache__ is
excluded from the commit.

Backfill delivered: reproducible scanner/census, five negative controls,
four isolated kernel-checked constructor cases, and resource/timing tooling.
No new sorry, axiom, native_decide, raised heartbeat budget or premise changes.
Full-source equality is stronger than a textual statement-only freeze for the
unchanged tree, but does not substitute for elaborated API compatibility.

## Resume

Retain this original VM/branch/goal; do not create a replacement goal. Obtain
live owner acknowledgement for AbiAccess through coordinator relay. Resolve
the out-of-scope Horizon baseline prerequisite with its owner/gate. Apply
approved directory repairs and repeat clean old/new runs with identical final
runner, module order, cache and resources. Complete affected and final gates,
API verification, reviews, performance escalation if worse (stop above 10%),
and migrate-root-gate handoff. The entire assignment remains unfinished.
