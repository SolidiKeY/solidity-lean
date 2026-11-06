# H62/H63 SortCheck migration checkpoint and blocked handoff

Batch `solidity-h62-6-20261106`, owner `migrate-sortcheck`. This is an isolated migration overlay, not live producer ownership. **Overall status: blocked, not complete.** No production `.lean`, toolchain, Lake configuration, generated root, module map, or axiom pin changed. No push, merge, PR, pre-gate, freeze announcement, or master publication occurred.

## Checkout and scope

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Checkout: `/workspace/migrate-sortcheck`. Branch: `codex/solidity-h62-6-20261106/migrate-sortcheck`. Original clean `/workspace/solidity-lean` branch `work` at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4` was preserved. The exact missing published base was fetched and verified an ancestor of `origin/master` before creating the assigned branch/worktree. Export metadata records the final full commit.

Read AGENTS, SortCheck rule-table conventions, intrinsic G0, module map, build/parallelism/resource instructions, and lean-verify skill. No Lean MCP tool was exposed; per-file CLI elaboration was used with explicit `-j1` and `--tstack=131072`. Repository final gates remain required. The runtime skill was read and network policy inspected. All coordinator input hashes match `/workspace/h62-coordinator-inputs/sha256.json`. `get_goal` is not exposed; the coordinator explicitly says its absence is not a blocker. No replacement goal was created.

## Queue accounting

| Checkpoint | Status | Evidence and missing work |
|---|---|---|
| 1. Census and old baseline | partial | Complete source census plus all 46 generated theorem entries and nested helper; old elaborated census has 658 declarations. All 64 dependency-closure modules pass on 4.24. Preliminary clean per-file elaboration timing measured; canonical matched Lake/native build gate still pending. |
| 2. Official toolchain and adaptation | partial | Official archive pin verified; actual Lean/Lake versions and new KeySort pass recorded. Annotations passes unchanged. Parser's two-line proposal passes only in isolated fixture. Exact-file owner acknowledgement and production adaptation pending. |
| 3. New build and performance | blocked | New closure fails in out-of-scope Syntax/Raw. Faithfulness cannot be validated. Parser-only fixture observation exceeds 10%; further Lean work STOPPED. Full matched timing and final validation pending. |
| 4. Reviewable export and interfaces | partial | Additive tooling/tests, source hashes, old complete interface/axiom capture, dependency report and proposed Parser patch exported. New complete interface comparison, final conformance/build gates, and root-gate acceptance pending. |

## Toolchain identity and resources

Required official archive: `https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst`.
SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` (exact coordinator pin).

- Old Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613`.
- New Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb`.
- VM: 16 GiB cgroup memory cap, four CPU quota, zero configured swap. Runner enforces 12 GiB per-process address-space cap plus sampled aggregate RSS limit, 4 GiB available reserve, no-swap check, 300s per-module safety timeout. One Lean process at a time, `LEAN_NUM_THREADS=1`, explicit `-j1`. Writer lock held throughout checks. No systemd-run, shared Lake/per-master cache, heartbeat increase, or toolchain-file override.
- RSS sampling interval is 100ms. Corrected runner additionally records kernel cumulative child high-water RSS, compiler/archive identity, runner hashes, and before/after source and prerequisite artifact hashes. Provenance hashing is outside the measured build interval. These are different metrics and are labelled separately.

## Results and proof boundaries

Old clean closure: **64/64 pass**, **374.214214s**, sampled aggregate peak **7081349120 bytes** (6.59 GiB). Initial harness lacked source snapshots/kernel high-water output; `old-clean-provenance.json` verifies every closure source against base and documents this limitation. This measures per-file elaboration/kernel checking into fresh private oleans, not native executable building or the full repository gate.

New clean closure: KeySort, AST, Annotations and SpecSyntax pass; Syntax/Raw fails at 597, 650, 665, 682/684 (String/Slice API mismatches). See `new-clean2/result.json` and its exact commands/logs. This source is read-only in this lane; its migration owner is routed in `cross-directory-dependencies.json`. No changes outside scope were attempted.

Original Parser fails on removed String.trim/dropRight APIs. Deterministic `fixture.py` changes only `l.trim` to `l.trimAscii.copy` and `(t.dropRight 1).trim` to `(t.dropEnd 1).trimAscii.copy`. New fixture Parser and all controls pass. Deprecated String.mk remains to keep the proposal minimal. This proposal has not been applied to production. History review preserves the earlier executable #guard boundary and generated annotation representation; no speed refactor was reversed.

Controls: **two kernel examples and 24 executable guards**, both old production Parser and new isolated Parser pass. Coverage includes comments, unknown tokens/sorts, missing/ambiguous generic varconds, memory/storage/net/default/length classification, legacy valAt, multiset ordering/multiplicity, missing/unannotated taclets, rendering, and annotation/operator inventories. Scanner suffix operations do not kernel-reduce in these examples; their checks are executable guards, not a new external-parser equivalence theorem. Earlier failed test/setup iterations remain evidence and are not accepted as passing checks.

Old interface capture: **658 declarations**, including generated/internal declarations from all three assigned modules, with complete printed types and transitive axiom sets. Log SHA-256: `85430e37388519d87672f7bd40ae3f12af7f66190f13011b064dd3d7e7cc818a`. Observed axiom union is only propext, Classical.choice, Quot.sound. No sorryAx or new trust shortcut was admitted. Printed text is an elaborated census, not proof of cross-version definitional equality. Source freeze protects exact original statements and budgets; new full capture remains pending.

## Performance STOP and dependency requests

Parser-only observed times: old **2.222039s**, new isolated fixture **2.824587s**, observed **+27.12%**. New fixture sampled RSS is also higher. These runs differ in source adaptation, compiler prerequisites, source root and harness revision; **no full-directory timing delta is valid**. `compare.py` rejects the available full reports with null delta because the new build failed and the original baseline lacks final provenance fields. Nevertheless the observed increase triggers conservative STOP under the assignment's >10% rule. No further Lean build, timing rerun, executable conformance run, or final gate was performed after observing it.

**ESCALATE PERF-01:** Keep Lean checks stopped pending coordinator review/dependency migration, or authorize one bounded matched Parser timing pair while retaining the same >10% stop gate. No gate waiver or statement change is proposed.

Saved requests in `coordination-requests.json`:

1. DEP-SYNTAX-01: syntax migration owner must supply the pinned-toolchain Syntax/Raw overlay/dependencies. Full report enumerates all 61 out-of-directory repository dependencies and their migration owners.
2. OWNER-PARSER-01: exact-file acknowledgement for Parser's two substitutions from coordinator/root migration and live producer before any existing-file edit. `relay.sh` is absent; the request is saved for coordinator routing, not falsely reported sent. Silence is not permission.
3. PERF-01: timing STOP above. The original goal stays unfinished; resume only within its authorization and resolved stop/dependency conditions.

## Frozen source hashes

- `Solidity/SortCheck/Annotations.lean`: `45bc9365a12b009a45a4352fd3fb6f6bf16098400beb7593dea8c40f5f060188`
- `Solidity/SortCheck/Faithfulness.lean`: `b006ff2d3243ae5b6a2510a1eae5e1e1d8459ba254ff16a89151054b4b67ea8b`
- `Solidity/SortCheck/Parser.lean`: `e21e62c46abaf7f954aaa3447033983d66ba75a1257217f16bacecc1d9a2d330`

Census records every source pattern-clause line and all generated theorem invocation metadata. Full environment capture supplies the elaborated declarations the lexical index cannot infer. No original statement, premise, exclusion, observation, proof budget, or generated row was changed. No axioms/sorry/native_decide added to production or tests. No helpers registered centrally; fixture/tests stay in the explicitly assigned test scope. H44 bulk logs/interfaces/generated experiments remain off git with manifest hashes.

## Reproduction and gates

All exact per-file commands, exits, wall/RSS data and source/artifact identity are in the named `result.json` files beneath `/workspace/migrate-sortcheck-evidence`. Representative commands from repository root:

```sh
python3 scripts/h62/item6/migrate-sortcheck/census.py
python3 scripts/h62/item6/migrate-sortcheck/selfcheck.py
python3 scripts/h62/item6/migrate-sortcheck/check.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out FRESH_OLD_DIRECTORY
python3 scripts/h62/item6/migrate-sortcheck/check.py --toolchain /workspace/migrate-sortcheck-evidence/toolchains/lean-4.35.0-linux --out FRESH_NEW_DIRECTORY
python3 scripts/h62/item6/migrate-sortcheck/fixture.py --out FRESH_FIXTURE_DIRECTORY
```

These are reproduction instructions, not authorization to bypass the current performance STOP. Focused controls use `--dependency-lib` with explicit artifact hashes; `--source-root` selects the isolated fixture. `--run`/`--run-args` supports future bounded conformance once unblocked; not yet exercised. Fresh output directories are mandatory. No implicit shared cache is read.

Passing non-Lean gates: tooling selfcheck (missing-module negative control, timing rejection/STOP controls, deterministic two-line fixture and checksum checks), layer check (857 core modules, no frontend reach), generated root `--check`, fragments `--check`, and scoped freeze check. Full `./run-lean.sh`, clean Lake/native build comparison and explicit frozen SolKey conformance execution remain pending, not waived. Frozen rule input SHA-256 is `02b7a995c9aaf1a856019d7071ca3e75a57de91b071c93b24ebf6ae7eef989eb`.

## Independent reviews and next handoff

Read-only finder and skeptic did not use Lean servers or write files. They found and prompted fixes for missing 46 generated theorem entries/nested helper, missing-target false pass, subprocess cleanup, RSS labels, source/prerequisite provenance, overlay conflicts, and invalid initial finite tests. Actual final passing controls supersede failed iterations. Final follow-up review confirms the blocked conclusions. The finder additionally required exact compiler/archive identity, matching runner provenance and numeric wall-time validation in the future timing subgate; these and same-compiler/mismatched-runner negative controls were added without rerunning Lean. Generated Python bytecode was removed and future local imports suppress it. Final reports are recorded in the off-git review report. Known limitations above remain required gates, not accepted exclusions.

Useful completed work items: source/declaration census and baseline; exact toolchain provisioning/prerequisite diagnostics; deterministic isolated scanner controls and tooling acceptance tests; reviewable blocked migration packet. Hand back to the coordinator after these items; do not self-launch a replacement thread or goal. The current VM/goal remain the continuation state. Export HANDOFF.md records absolute patch/bundle/evidence/checksum paths and full committed head. No RUNTIME_GATE_PASS is claimed for full migration.
