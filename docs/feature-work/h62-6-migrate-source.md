# H62/H63 Source migration overlay

Owner: `solidity-h62-6-20261106/migrate-source`. Branch:
`codex/solidity-h62-6-20261106/migrate-source`. Pinned base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/solidity-h62-6-migrate-source`.
The original clean `/workspace/solidity-lean` work checkout was preserved.
Base was fetched from origin and verified an ancestor of origin/master before
creating this worktree. No push, merge, registration, producer ownership transfer,
central pin edit, or toolchain cut-over has occurred.

## Checkpoint state

1. **Partial:** census covers exactly the 199 explicitly owned Source files and
   246 local prerequisite modules. It records 4,428 lexical declaration
   candidates, 47 external local modules, 11 external direct imports and 489
   external consumer edges. Header reconciliation and negative controls pass.
   Byte hashes freeze all original Source statements, definitions and budgets;
   they do not establish elaborated cross-version API equivalence. Full imported
   constant/constructor/recursor inventory fixture is prepared, not yet validated.
   Accepted complete clean old baseline remains pending.
2. **Blocked:** exact official target archive is installed privately and matches
   coordinator SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
   Target Lean is 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
   Lake is 5.0.0-src+eb6cafb. Bounded target KeySort passes. Diagnostic closure
   run: 15 passed (5 Source), 3 failed, 228 import-blocked. See owner requests.
3. **Blocked:** all-module new build, accepted complete old/new wall/RSS comparison,
   affected acceptance and final repository gate remain pending. Timing delta is
   undefined; incomplete runs cannot establish the <=10% regression gate.
4. **Partial:** deterministic tooling and an isolated proof candidate are prepared
   for root/gate review. Final patch/bundle and checksum handoff follow validation.

## Reproduction and resource policy

All bulk evidence is outside git at `/workspace/h62-migrate-source-evidence`.
Coordinator inputs at `/workspace/h62-coordinator-inputs` all match sha256.json.
The tracked lean-toolchain stays at v4.24.0. Private absolute compiler paths
select the official target. Baseline Lean: 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
The downloaded old release archive SHA256 is
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.

Tooling lives in `scripts/h62/item6/migrate-source/` and acceptance fixtures in
`tests/h62/item6/migrate-source/`. Commands are documented in each script's CLI
or header. `census.py --out PATH` reads the pinned git objects;
`acceptance.py CENSUS` independently reconciles all import headers and checks
comments, strings, complete owned-file/order coverage and local dependency order.
`generate-api.py CENSUS OUTPUT` emits the Inventory fixture reproducibly.
It records every imported Source constant, including constructors and recursors,
with its defining module, universe parameters, kind and internal type representation.
The representation is compiler-dependent observation, not semantic equality proof.

`build.py --root ROOT --toolchain TC --census CENSUS --out FRESH_DIRECTORY`
runs one compiler at a time, explicit `-j1`, LEAN_NUM_THREADS=1, 10,000 MiB Lean
heap bound, sampled 12 GiB group-RSS stop and a 4 GiB available-memory guard.
The kernel-enforced hard bound is the VM cgroup; no virtual-address cap is used.
The VM has a 16 GiB cgroup cap, four CPU quota and no system swap. No systemd-run.
The repository writer lock spans every build. Fresh private import paths are
forced *after* lake env. Both Lake and Lean executables are absolute.
The measurement builds oleans for the closure; it is not the final run-lean.sh
repository gate or native executable/test compilation.
Reports record each command/exit/wall time and sampled process-group RSS at 50 ms.
Resource stops preserve the failing module and are never passing checks.

Initial old-clean-01 was interrupted to fix finder/skeptic tooling findings.
Old-clean-02 stopped safely in Horizon at a per-module 389.706 s and 4,834,746,368 sampled RSS
bytes because provisioning left 7.3 GB clean file cache. It is failed evidence.
Task-private clean-page eviction via cold-cache.py reduced cgroup usage from
7.7 GB to 0.55 GB without changing files, limits or global cache settings.
Before each accepted measurement, run the same roots:

```sh
python3 scripts/h62/item6/migrate-source/cold-cache.py \
  /workspace/h62-migrate-source-evidence /workspace/.setup/tools/lean-4.24.0-linux
```

## Exact-file owner coordination and backfill

The saved `owner-requests.json` is the self-contained coordinator relay request.
No relay.sh exists on this VM. Existing originals remain read-only pending reply.
MS-DEP-HASH requests migrate-hash's CollisionBound proof compatibility patch.
MS-DEP-SYNTAX requests migrate-syntax's Raw String/Slice API compatibility patch.
MS-OWNER-CTOR requests coordination with the live Source producer before touching
only the nodes_eq/excl_ctor proof bodies. No absent reply is treated as consent.

The generated Ctor fixture contains the exact pinned definitions and theorem
headers. Its proof-only candidate uses constructor-head congruence to avoid
recursive simplifier expansion, and explicitly cases Boolean tests before
conditional elimination. The full 112-constructor completeness proof is retained.
No statement, premise, exclusion, observation, axiom policy or proof budget changes.
First candidate failed and its sorryAx printouts are rejected failure evidence.
The revised candidate passed on old (63.549 s, 1,561,919,488 sampled RSS bytes)
and new (21.636 s, 710,295,552 bytes); both changed theorem axiom sets are [propext].
These fixture observations are not a clean all-directory performance comparison.
Final unused simp-argument cleanup must be rechecked before accepting the patch.
No original Source declaration was edited. Lexical Source sorry/axiom/native_decide
counts are all zero. Failed elaboration's synthetic sorryAx is never accepted.

## Independent reviews

Independent read-only finder and skeptic used neither Lean server nor Lean jobs.
Both found and confirmed fixes for Lake prepending workspace artifacts and missing
resource-stop rows. Finder prompted absolute compiler paths; skeptic prompted
complete assigned-module/order coverage. Both accepted the preparatory scanner
scope, while retaining elaborated inventory and full validation as outstanding.
Both rejected the first Ctor candidate. Finder and skeptic found a cold-cache path
prefix acceptance bug; it now uses resolved path containment. Further candidate
and handoff reviews remain pending.

## Proof versus external checks and unfinished obligations

Per-file diagnostics use the bounded CLI because no Lean MCP tools are exposed.
The isolated fixture checks kernel-elaborated proofs, while the census, resource
sampling and scanner controls are external tooling observations. No fixture pass
certifies the unchanged failing Source original or blocked imports. No
RUNTIME_GATE_PASS is asserted. Required work still includes owner coordination,
external dependency overlays, applying/rechecking the owned proof repair, full
old/new clean comparison, elaborated interface reconciliation, final affected
validation/reviews, and the root/gate migration handoff. No goal completion claimed.

## Resource instrumentation correction (checkpoint 2)

Old-clean-03 failed at Horizon after 461.294 s (whole failed run 1013.790 s),
5,606,068,224 sampled RSS bytes, std::bad_alloc and zero cgroup OOM/max events.
Its self-imposed 12 GiB RLIMIT_AS was an incorrect proxy for resident RAM.
Finder and skeptic supported removing that virtual restriction while retaining
all resident/proof budgets. The corrected Horizon single-file feasibility probe
passed at 715.030 s, 8,110,936,064 sampled RSS bytes and 16,827,170,816 diagnostic
virtual bytes; inherited RLIMIT_AS is unlimited. The original source SHA256 is
f579466b9b961c899a4cb2bbe3948a8143284b186e8035c30395c6b89a7d9cd4.
This probe reused exact private imports and cannot establish a clean full build.
Only a new complete clean run under the corrected harness can establish baseline.
The earlier address-limited results are failed diagnostic evidence.

Final fixture reports now bind input SHA256 and actual compiler version before
launch, check the input remains unchanged, and retain RSS/VMS/failure data.
compare.py rejects failed/incomplete builds, changed module order/resource
profiles and invalid metrics. Any regression returns escalation; >10% returns
STOP. Synthetic negative controls are acceptance of that refusal logic, not
measured source performance. The actual comparison remains blocked.
