# H62 migrate-syntax: blocked migration overlay

Assignment: solidity-h62-6-20261106/migrate-syntax. Repository:
`/workspace/solidity-lean-migrate-syntax`; branch
`codex/solidity-h62-6-20261106/migrate-syntax`; pinned base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Original clean checkout `/workspace/solidity-lean` remains on `work`.
The base was fetched from origin, verified as an ancestor of origin/master,
and used to create an isolated worktree without discarding existing work.

This is a partial, blocked handoff, not completion or RUNTIME_GATE_PASS.
No production Lean file, frozen statement, premise, exclusion, proof budget,
root, module map, axiom pin, lakefile or lean-toolchain was edited. New Lean
helpers: none. New sorry/axiom/native_decide: zero. No push, merge or PR.
Live producer ownership remains unchanged.

## Evidence and reproduction

Bulk outputs are off git at `/workspace/migrate-syntax-evidence`.
Reproducible tooling lives in `scripts/h62/item6/migrate-syntax/`;
lightweight acceptance is `python3 tests/h62/item6/migrate-syntax/accept.py`.
The fixture generator emits only an off-git, UNAPPROVED candidate. Its
output must never be mistaken for an approved production migration.

Official pinned archive:
`/workspace/migrate-syntax-evidence/toolchains/lean-4.35.0-linux.tar.zst`;
SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The coordinator inputs at `/workspace/h62-coordinator-inputs` match their
sha256.json manifest, including toolchain-pin.json. Old Lean reports
4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; old Lake
5.0.0-src+797c613. New Lean reports 4.35.0, commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc; new Lake 5.0.0-src+eb6cafb.
Both official Linux release builds, x86_64.

The direct compiler probe uses explicit `-j1 -M11000 --tstack=131072`,
LEAN_NUM_THREADS=1, CPU affinity {0}, empty private output directories and
no Lake cache. A 16 GiB VM cgroup and empty /proc/swaps were observed;
the runner checks a 4 GiB host/cgroup reserve throughout each module.
No systemd-run. The cgroup swap.max is unrestricted, but no host swap is
configured. OS wait4 records per-process maximum RSS; this is not an
aggregate process-tree measurement. A 300-second per-module time bound
and bounded TERM/KILL resource-stop path are implemented.

Commands (run from the assigned worktree):

- `python3 scripts/h62/item6/migrate-syntax/census.py --output /workspace/migrate-syntax-evidence/census-v2.json`: exit 0; 21 assigned files, 29-module local closure, eight external local dependencies, five toolchain imports, 873 lexical declaration starts, 273 command starts, 3204 case/pattern lines. These are lexical coverage aids, not a complete Lean parser or generated-declaration census.
- `python3 scripts/h62/item6/migrate-syntax/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --output /workspace/migrate-syntax-evidence/old-clean-2`: exit 0; all 29 modules pass, 218.691 seconds wall, 885164 KiB peak per-process RSS. This run used the pre-review runner: its final 29-module outcome is valid, but its live status prematurely said pass. Corrected tooling now writes running until completion and records expected/completed counts. A corrected clean repeat remains pending the performance hold.
- `python3 scripts/h62/item6/migrate-syntax/measure.py --toolchain /workspace/migrate-syntax-evidence/toolchains/lean-4.35.0-linux --output /workspace/migrate-syntax-evidence/new-clean-1`: exit 1; original Raw fails at lines 597,650,665,682,684 on String/Slice API differences. Seven external local prerequisites pass; the external umbrella Solidity.Syntax is blocked by the Raw/Grammar chain. CheckedExact also passes. Failed/incomplete runs cannot establish a whole-directory performance ratio.
- `python3 scripts/h62/item6/migrate-syntax/fixture.py --output /workspace/migrate-syntax-evidence/fixture-2`: exit 0; emits Raw/Grammar candidate only, production unchanged.
- `python3 scripts/h62/item6/migrate-syntax/measure.py --source-root /workspace/migrate-syntax-evidence/fixture-2 --toolchain /workspace/migrate-syntax-evidence/toolchains/lean-4.35.0-linux --output /workspace/migrate-syntax-evidence/new-fixture-2`: exit 1; visits 29 modules: 20 pass, Context fails at line 95 (String.Slice passed where String required), eight dependent modules blocked. Raw and Grammar candidate modules pass. This completed before attempted cancellation; final status is fail, not a cancellation pass.
- `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-syntax/accept.py`: exit 0; deterministic census, attributed/command coverage, comment/string and missing-import/cycle negative controls, incomplete-run/settings rejection, wall/RSS STOP controls pass.
- `git diff --exit-code c6f550e281a7e5affa9a99bc2cdaed556dec00e4 -- Solidity lean-toolchain lakefile.toml`: exit 0; all production source preserved exactly.

An initial timing setup attempt failed before Lean because /usr/bin/time
was absent. Package installation was unavailable to the VM user; the
runner uses wait4 instead. The partial old-clean-1 directory is not a pass.
No auto-review rejection occurred.

## Checkpoints and blockers

1. Census and clean old assigned-closure probe exist. Full elaborated API
   census, corrected measurement repeat, required KeySort/sort-check output
   and repository final gate remain pending; checkpoint partial.
2. Official coordinator-pinned toolchain verified. Original directory fails;
   candidate fixture repairs Raw and Grammar. Exact-file owner coordination
   for Raw, Grammar and Context is pending: no relay.sh was discoverable
   on this VM and absence of reply grants no edit permission. Checkpoint blocked.
3. Further heavy probes are held for an RSS regression. On identical unchanged
   AST sources/settings, RSS rose 739820 -> 1515860 KiB (+104.9%), while wall
   improved 10.309 -> 6.231 seconds. Matched prerequisites show similar memory
   increases. Full successful old/new comparison is unavailable. ESCALATE:
   root gate must resolve whether the >10% STOP covers RSS or only wall slowdown;
   do not silently waive the memory regression. Checkpoint blocked.
4. Tooling patch, candidate patch, source fingerprints and cross-directory
   dependency report are prepared. Root-gate delivery/receipt and final validated
   migration bundle remain pending. Checkpoint partial.

`owner-request.json`, `performance-escalation.json`, `source-preservation.json`,
`frozen-source-sha256.txt`, `cross-directory-dependencies.json` and all module
logs/results are in the evidence directory. Source hashes prove unchanged
source identity only; no elaborated frozen-interface hash or semantic
migration-equivalence proof is claimed. Concrete fixture compilation and
Python negative controls supplement the original Lean proofs; they do not
prove parser equivalence for arbitrary inputs. No statement was weakened.
The String replacements use explicit slice copies, character-list drop,
explicit method arguments and the renamed dropEnd/String.ofList APIs.
They still require owner review and full semantic/consumer validation.

Required pending gates: all original assigned modules on 4.35.0, passing
KeySort and actual SolKey sort-annotation output, affected examples/TestSuite,
repository-policy ./run-lean.sh final gate, clean accepted before/after
wall/RSS comparison, elaborated frozen API hashes, final independent reviews
and root-gate handoff. No outside-scope dependency migration was attempted.
The original persistent goal must remain unfinished; a blocker outcome
preserves these obligations. Coordinator receives fresh-thread handoff after
3-5 completed items; no replacement goal/thread is launched here.

## Independent read-only reviews

Finder and skeptic each reviewed independently without Lean/server use.
Both found premature live-pass status, a comment parsed as import at
Elab/Values line 934, and omitted attributed Scoped theorems. Fixed using
running/final counts, nested comment/string filtering, and attributed plus
indented declaration scanning; syntax/macro/elab and case-line coverage was
added. Acceptance exercises all confirmed scanner/status defects.
The finder recommended a bounded KILL fallback, now present. Both require
explicit distinction between source hashes/API hashes and closure probes/full
gates. Final re-review confirmed the three initial fixes. The skeptic caught a floating-point threshold error at exactly 10%; comparison now uses Fraction/integer thresholds, and exact-10% controls require escalation without STOP. Acceptance passes with this correction. The legacy old baseline lacks expected/completed counters, so compare.py correctly refuses that raw file; preserve it rather than silently converting its metadata. Full final migration review remains pending.

Final static checks pass: check-layers reports 857 core modules, zero reaching elaborators or checked parser adapters; register.sh --check and fragments.sh --check each exit 0. Final read-only skeptic verifies exact 10% escalates and 11% stops for wall/RSS; no further confirmed tooling defect. Independent review details: `/workspace/migrate-syntax-evidence/reviews.json`.
