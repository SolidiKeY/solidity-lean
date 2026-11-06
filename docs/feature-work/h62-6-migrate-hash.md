# H62 item 6 migrate-hash: blocked migration candidate

Repository `/workspace/migrate-hash`, branch `codex/solidity-h62-6-20261106/migrate-hash`,
pinned base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
`origin/master` was fetched and base ancestry verified. The older clean `work`
checkout at `/workspace/solidity-lean` was preserved. This branch was created at
exactly the base; no push, merge, PR, cut-over or live-producer ownership transfer.
The exported result records the full committed head after this document's commit.

| Checkpoint | State | Evidence / remaining work |
|---|---|---|
| 1. Pinned census and clean old build | done | 125 declarations; native old-toolchain Hash build passes with fresh cache and canonical names |
| 2. Identical new toolchain and adaptation | blocked | Official pin verified; proof-only candidate passes; existing-file owner response pending |
| 3. New build and performance | blocked | Canonical candidate native build passes; RSS escalation and full affected/runtime gates pending |
| 4. Patch, hashes and root handoff | partial | Exported candidate and evidence ready for retrieval; root-gate acceptance pending |

## Toolchain and fixed resources

Official `leanprover/lean4:v4.35.0`, archive `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`, matches
`/workspace/h62-coordinator-inputs/toolchain-pin.json`. All five coordinator input
files match the supplied SHA256 manifest. No v4.24 per-master cache was restored.

Old Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release.
Old Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
New Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
New Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Bounded KeySort passes on both toolchains before Hash checks. No Lean MCP tool is
exposed; checks use the repository's per-file `lake env lean` command and native Lake.

The VM has a 16 GiB memory cgroup and zero configured swap. Every heavy job holds
the repository writer flock and runs serially with `LEAN_NUM_THREADS=1`, explicit
`-j1`, `--tstack=131072`, a 12 GiB address-space ceiling, a monitored 4 GiB effective
available-memory reserve and a 300 second per-module timeout. No systemd-run.
Every final run snapshots and hashes consumed sources before execution and verifies
them unchanged afterwards. No tracked toolchain/configuration/registry is modified.

## Census and candidate

`CollisionBound` imports nothing; `Adaptive` imports only `CollisionBound`.
84 + 41 original declarations include 97 theorems, 24 named definitions and four
anonymous decidability instances. Signature/context/import and definition-body
hashes match the pinned originals after normalizing only the fixture import path.
The lexical signature audit supplements kernel checks; it is not a kernel type hash.
Original whole-source hashes (the production files remain byte-identical):

- `Solidity/Hash/CollisionBound.lean`: `49e8b756f01c78c6e850401ba29ac4e65b71ce3d091a2ccee02e2291a6d9e7ce` (84 declarations).
- `Solidity/Hash/Adaptive.lean`: `4aab278cc5f94bb8b00827b06b44ca2ac05fe2610038054a5821fcb638bf3779` (41 declarations).

The new-toolchain original build fails at `countP_contains_le`, `countP_near_le`,
and `countP_covers_le`; the untouched axiom guards reject the resulting incomplete
proofs. Isolated Adaptive checking additionally exposes the two zero-query cases
of `two_mul_eagerCollides_le` and `two_mul_eagerRegionsFail_le`.
The candidate uses explicit `List.contains_cons`, explicitly extracts propositions
from `decide`, and proves the two zero-query negations directly. Deprecated `if_*`
lemma uses become the official `ite_*` names. No definition body, theorem type,
premise, exclusion, observation, axiom guard or proof budget changes. No new axiom,
sorry, native_decide, trust shortcut or raised maxHeartbeats. History was inspected;
no speed-motivated refactor was undone. This is a proof compatibility repair.

All 121 named APIs, all 97 theorem axiom sets and the four anonymous instances pass.
The only observed axiom names are `propext`, `Classical.choice`, and `Quot.sound`;
14 theorems have empty axiom sets. Nineteen `decide +kernel` controls distinguish
repeated queries from collisions, noninjective functions on singleton/repeated
runs, wrapped region overlap/root hits, zero-width regions, counting boundary
cases, step hits and zero-query stopping. Six negative scanner controls and
statement/definition-body mutation checks pass. These finite checks supplement
universal proofs; no external EVM or solc test result is claimed.

## Clean native measurements and escalation

The final runs are `/workspace/migrate-hash-evidence/old-lake-clean-3` and
`new-lake-clean-2`. Each creates a new private package with canonical module names,
identical minimal Lake configuration, no dependency, and cache disabled. Commands
are `lake --no-cache -v build Solidity.KeySort:o`, then the same command for
`Solidity.Hash.CollisionBound:o` and `Solidity.Hash.Adaptive:o`, one at a time.
Verbose logs show actual Lean C generation and clang object compilation. Measurements
use monotonic wall time and OS wait4 child/descendant maximum RSS. These are clean
Hash builds in private snapshots, not a whole-repository performance claim.

| Module | Old wall s | New wall s | Delta | Old peak KiB | New peak KiB | RSS delta |
|---|---:|---:|---:|---:|---:|---:|
| Solidity.KeySort | 2.4673 | 2.0513 | -16.86% | 264624 | 512696 | +93.75% |
| Solidity.Hash.CollisionBound | 6.9928 | 4.6648 | -33.29% | 423884 | 600300 | +41.62% |
| Solidity.Hash.Adaptive | 2.7714 | 2.0714 | -25.26% | 317256 | 536652 | +69.15% |

Combined Hash wall: 9.7642 → 6.7362 seconds
(-31.01%). No individual or aggregate >10% wall slowdown.
**ESCALATE Q-HASH-RSS:** RSS increases remain unresolved. Faster wall time does not
clear this regression. Options and exact evidence are in `coordination.json` and
`/workspace/migrate-hash-evidence/performance.json`. No final runtime-pass claim.

## Cross-directory handoff

Direct external importers: `Solidity/Storage/HashedLayout.lean`,
`Solidity/Roadmap/Contracts.lean`, `Bridge/SolidityBridge/HashBridge/Queries.lean`,
and the generated root. They remain read-only. There are no incoming dependencies
outside Hash. Root migration must validate these consumers and their transitive
affected closures using the identical toolchain. No new production module exists,
so the registration fragment is empty; generated roots, central maps and axiom
pins are unchanged. Bridge validation remains an external/optional dependency gate.

**ESCALATE Q-HASH-OWNER:** the required `scripts/coord-tools/relay.sh` is absent at
the base and no alternate coordinator relay/owner response is available. Exact-file
request: apply the exported candidate to `Solidity/Hash/CollisionBound.lean` and
`Solidity/Hash/Adaptive.lean` as a migration-only overlay. Options are to provide
the relay/owner response for this worker, or have the owner apply the candidate.
Absent reply is not permission; neither production file was edited. The final
lean-toolchain edit belongs to migrate-root-gate.

Pending: owner coordination and production overlay, RSS regression disposition,
full affected importer validation, `./run-lean.sh` in the root migration environment,
and migrate-root-gate receipt. No claim that a snapshot build replaces these gates.
In-scope backfill completed: declaration census, negative scanner controls, isolated
fixture proofs, all-declaration API/axiom checks, semantic controls and deterministic
measurement/export tooling. No newly unclaimed cleanup scope was taken.

## Independent read-only reviews

Finder and skeptic ran independently, without Lean/server calls or edits. Both
confirmed actual frozen statements, definition bodies and proof budgets unchanged.
Findings fixed: guaranteed kill/reap on timeout/resource exceptions; fail-closed
scanner handling of modifiers/indentation/standalone attributes; definition-body
hashes; explicit four-instance checks; source-bound logs including Inventory and
Controls; and >10% slowdown stop per module as well as aggregate. Final reviews
approve this partial evidence handoff, explicitly retaining the owner, RSS and
full-gate blockers. Full review record is `/workspace/migrate-hash-evidence/reviews.md`.

## Gates and retrieval

Native old/new builds: exit 0 in their `results.json`; prerequisite KeySort passes.
Final per-file API/axiom/control acceptance: `new-acceptance-3/results.json`, all five
commands exit 0 with empty proof/control error logs. Source-bound audit:
`python3 scripts/h62/item6/migrate-hash/acceptance.py /workspace/migrate-hash-evidence`,
exit 0, `acceptance-audit.log`. Static layer check passes (857 core modules; zero
reach elaborator/checked-parser adapters); generated roots and fragments checks pass.
Patch applicability and whitespace checks pass. The global documentation-path check
exits 1 on the pre-existing unavailable Mathlib reference in
`docs/feature-work/after-roadmap-va1.md` to
Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean; that citation exists at the
pinned base and lies outside this lane. Scoped Markdown links resolve. Failed
initial builds are retained.

Artifacts after committed export: `/workspace/migrate-hash-evidence/original.patch`,
`migration-candidate.patch`, `migration.bundle`, `evidence.tar.gz`, `SHA256SUMS`,
`result.json` and `HANDOFF.md`. Generated bulk fixtures, inventories and logs remain
off git; generators and finite controls are committed. Reproduction instructions:
[scoped README](../../tests/h62/item6/migrate-hash/README.md).

The existing persistent goal must remain unfinished. The worker did not create or
reset a goal. `get_goal` is absent, as explicitly permitted by coordinator steering.
Resume this exact branch/VM after blockers resolve; a fresh-thread handoff goes to
the coordinator, never to a self-created replacement goal.
