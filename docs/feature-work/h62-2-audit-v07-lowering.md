# H62 item 2: v07-lowering audit — blocked proof validation, preliminary backfill

Repository: /workspace/solidity-lean
Branch: codex/solidity-h62-2-20261106/audit-v07-lowering
Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4
Initial checkout: clean branch work at 6cf853aea0417155aca29ddb91f1767d3f3a3cc4. Fetched origin/master at 821e3e8f4c7a5ac3a51dc5cba8be813bb173e310; git merge-base --is-ancestor BASE origin/master exited 0. Created assigned branch at BASE without resetting existing work.

This is a reviewable tooling checkpoint, not completion of any of the four audit checkpoints. No frozen statements touched; no Lean declarations/helpers added; new sorry/axiom count zero. No registered roots, central maps, cache pins, producer originals or H55 work changed.

## Queue and evidence boundary

1. Inventory: partial lexical backfill, 162 mapped modules / 968 theorem/lemma tokens, each unique by file and offset. All candidates retain pending premise classification, simultaneous witness and elaborated statement fidelity. Local names and source-tail hashes are NOT exact frozen signatures. Structure-field contracts, fully qualified names, inherited section parameters and interface/hypothesis classification remain to do.
2. Simultaneous witnesses: pending; no proof claimed. Unchanged dependency migration prevents checking the full mapped import closure.
3. Supported-program success/totality: pending, including reject-all/always-revert negatives and observable failure/gas/fork boundaries. No fabricated supported-program premise.
4. Verified witness/fidelity census: pending; all 968 candidates currently uncovered, owner V07 (v07-v11/v07-lowering), subject to exact statement classification. This count is preliminary and includes statements without hypotheses. It is not an exhaustive interface-contract certificate.

No V07 theorem has been established weakened/vacuous in this checkpoint, so no vacuity ESCALATE is invented. DEP-MIGRATION-001 is an external dependency compiler blocker. Static backfill remains possible and unfinished; this handoff does not assert every backfill obligation is blocked or complete.

## Reproduction and actual gates

All evidence under /workspace/h62-audit-v07-evidence, bulk off Git. All five coordinator-input hashes matched sha256.json. Official archive SHA256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d matched toolchain-pin.json.

- Branch/base/remote ancestry check: pass, git merge-base --is-ancestor BASE origin/master, exit 0.
- Official lean --version: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release. lake --version: Lake 5.0.0-src+eb6cafb (Lean 4.35.0).
- KeySort: LEAN_NUM_THREADS=1, ulimit -v 12582912; official lean -j1 --tstack=131072 Solidity/KeySort.lean: exit 0, Bash real 1.235s. Output keysort.log. Initial timing wrapper exited 127 because /usr/bin/time absent; rerun used Bash time.
- census.py --output /workspace/h62-audit-v07-evidence/census.json: exit 0. Repeated to census-repeat.json; cmp exit 0, deterministic 162/968. census-check.log.
- PYTHONDONTWRITEBYTECODE=1 flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/h62/item2/audit-v07-lowering/check-imports.py --repo /workspace/solidity-lean --toolchain /workspace/h62-audit-v07-evidence/toolchain/lean-4.35.0-linux --evidence /workspace/h62-audit-v07-evidence/import-check: exit 1. First unchanged module Solidity.Hash.CollisionBound fails after 3.414s; import-check/results.json records exact argv, source hash and timing. Details in owner ticket.
- Full ./run-lean.sh, affected Lean proofs, acceptance, axiom checks and before/after timings: pending. No RUNTIME_GATE_PASS or full gate claim. No refactor made; comparative timing delta unavailable. Do not infer <=10% slowdown from KeySort.

Runtime: approximately 17GiB visible memory, no system swap, enclosing cgroup memory.max=17179869184. Compiler serial with -j1, LEAN_NUM_THREADS=1, 12GiB address-space cap, four-GiB available-memory checks every 0.1s, 300s per module. No systemd-run or old v4.24 cache used. Direct compiler driver checks frozen import closure only, not repository acceptance. No Lean MCP exposed.

## Reviews and handoff

Independent read-only finder and skeptic confirmed counts and pending boundaries. Both found resource-monitor/result-recording gaps; fixed. Both found a stale status variable after the fix; corrected and reproduced compiler exit 1. Final reviews confirm no remaining tooling findings for this run. Full review summary: /workspace/h62-audit-v07-evidence/reviews.txt. Neither used Lean/server or changed files.

Owner ticket: tests/h62/item2/audit-v07-lowering/owner-ticket.md. relay.sh absent; ticket saved for coordinator retrieval, not sent. No source-edit authorization assumed. Resume on this same branch/base with coordinator-supplied statement-preserving migration overlay; never silently change base or toolchain. The original persistent goal was supplied; get_goal absent and optional per coordinator, no new goal created.

Artifacts: /workspace/h62-audit-v07-evidence/original.patch; handoff.json (full committed head/base/paths); SHA256SUMS. No push, merge, PR, pre-gate or deployment. All four checkpoints remain unfinished.
