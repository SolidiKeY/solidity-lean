# H62 item 6: migrate-stipend

Status: blocked by owner migration of `Solidity/Syntax/Raw.lean`; persistent goal incomplete.
Repository: `/workspace/solidity-lean`. Branch: `codex/solidity-h62-6-20261106/migrate-stipend`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`, fetched explicitly and verified ancestor of fetched `origin/master` (`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`). Started from clean unrelated `work` at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`; preserved that branch. No push, merge, root/toolchain edit or live-owner transfer.

## Checkpoints

1. Done: census all 31 explicit source declarations and 45 pattern rows, all 12 closure sources equal base, clean old build and independent reviews.
2. Partial: official coordinator-pinned toolchain installed and hash-verified; compatibility blocked outside scope. No original declarations, statements, proof budgets or types changed.
3. Blocked: new closure stops before Stipend. Complete before/after timings, affected validation and `./run-lean.sh` are pending. No RUNTIME_GATE_PASS claim.
4. Partial: reviewable scripts/fixtures, source guards, owner report and patch/bundle export prepared. Cross-version elaborated interface equality remains pending.
Backfill done: deterministic census, complete original source-case inventory, isolated 14-case acceptance/negative/boundary controls and top-level declaration type dump. No unclaimed work or H55 work taken.

## Frozen surface and imports

Only original directory module: `Solidity/Stipend/Rule.lean`. Exact source SHA256 `2b150ea2b3fe2187a9b642eaa4109ef2e987bc9e1884cfbe5e854786d09fbc86` at base and now. Zero new sorry/axiom/native_decide; no maxHeartbeats changes. Original axiom #guard_msgs pass on old compiler. No compiler Fitted/Enforced theorem is claimed by these controls.

Direct imports: `Solidity.Syntax.Scoped` (migrate-syntax) and `Solidity.Roadmap.Evm` (migrate-roadmap). Remaining closure: KeySort, AST, SpecSyntax, Syntax.Raw, Syntax.Grammar, Syntax.Contract, Syntax, Scope, Keccak. Root files belong migrate-root-gate. Direct downstream importer: `Solidity/Semantics/Nondeterminism/ForkStipend.lean` (migrate-semantics); its final affected gate is pending. Full dependency/source-hash map: `/workspace/migrate-stipend-evidence/census.json`.

Old top-level-source declaration type dump SHA256 `f87d8a169f2f66d3719c3538bf90ed55b806554d5269ed776f6374c6eb6df670`: `/workspace/migrate-stipend-evidence/old-fixtures/Interface.log`. It contains full printed types for 30 explicit names plus anonymous instance synthesis. It does not enumerate all generated structure fields/recursors; exact original whole-source guard also applies. No cross-version elaborated equality has been established. Fixtures stay under tests; no module/root/axiom registration needed or changed.

## Toolchains, resources and measurements

Official pin: `leanprover/lean4:v4.35.0`; archive `/workspace/migrate-stipend-evidence/toolchains/lean-4.35.0-linux.tar.zst`; SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` matches supplied toolchain-pin.json. All five coordinator input hashes verified.

Old Lean: 4.24.0 release, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
New Lean: 4.35.0 release, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake 5.0.0-src+eb6cafb.

VM cgroup: 16 GiB memory, CPU quota 4 cores, 0 swap in use. No systemd-run. Every Lean invocation serial `-j1 -M10000 --tstack=131072`, LEAN_NUM_THREADS=1. Monitor enforces 12 GiB RSS cap, min(host/cgroup) 4 GiB reserve, 300-second per-module limit and no swap use. No stops fired. Explicit output paths and LEAN_PATH prevent .lake/per-master artifact reuse; fresh output directory required. Clean means compiler outputs are absent, not OS page-cache eviction. Initial additive tooling creation preceded lock acquisition (procedural deviation); subsequent repository writes and all Lean runs held the required writer lock. No competing writer observed.

Authoritative old-clean-2: all 12 modules pass, wall 52.038961 s, run child high-water RSS 824264 KiB. Stipend alone: 2.831414 s, sampled RSS 612368 KiB. New-clean-2: fails after four attempts in 10.579145 s; three prerequisites pass, Raw fails. No full timing delta or slowdown conclusion. RSS increase observed in prerequisites is escalated in blockers.json. Historical clean-1 runs predate instrumentation fixes and are diagnostic only.

## Commands and decisive outcomes

Run from repository, inside `flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock`:

- `python3 scripts/h62/item6/migrate-stipend/census.py`: deterministic identical output twice; 31 declarations, 45 rows, 12/12 base-source checks true. scanner-checks.json.
- `python3 scripts/h62/item6/migrate-stipend/build.py /workspace/.setup/tools/lean-4.24.0-linux/bin/lean /workspace/migrate-stipend-evidence/old-clean-2`: exit 0; report.json records all commands, versions, wall/RSS and logs.
- Same runner with `/workspace/migrate-stipend-evidence/toolchains/lean-4.35.0-linux/bin/lean` and `new-clean-2`: exit 1. Both toolchains pass bounded `Solidity.KeySort` (empty log, exit 0). Raw has five errors: drop now produces String.Slice, missing Slice.toList/String.dropRight and polymorphic endsWith application. Exact lines 597, 650, 665, 682, 684. Log: new-clean-2/Solidity_Syntax_Raw.log.
- Old runner with output `old-fixtures`, `--fixture tests/h62/item6/migrate-stipend/Acceptance.lean --fixture tests/h62/item6/migrate-stipend/Interface.lean`: exit 0, both fixtures pass; old-fixtures/report.json and individual logs.
- `node scripts/check-layers.mjs`: exit 0, 857 core modules, zero reach elaborator or checked parser adapters.
- `bash scripts/coord-tools/register.sh --check` and `bash scripts/coord-tools/fragments.sh --check`: both exit 0. static-checks.json.
- `./run-lean.sh`: pending, not run or counted as pass; blocked until dependency migration allows new-toolchain build. Full affected consumers and final root gate remain obligatory.

Lean MCP tools are not exposed; used bounded direct compiler checks, not a replacement claim for the final repository gate. get_goal is not exposed; coordinator confirmed this optional inspection absence is not a blocker. No replacement goal created.

## Reviews and owner handoff

Independent read-only finder `/root/finder` and skeptic `/root/skeptic`, neither used Lean/server, found and rechecked fixes to cgroup reserve, closure provenance, cumulative RSS labeling and source/type claim boundaries. Both approved static backfill scope/trust shape. Detailed results: `/workspace/migrate-stipend-evidence/reviews.txt`.

Typed request DEP-SYNTAX-RAW-435 to migrate-syntax: provide owner-reviewed migration of exact file Raw.lean with provenance/source hashes. This lane has not edited it or requested scope expansion. Coordinator retrieves saved request; no relay.sh is present locally. Root-gate receives blockers.json, census and exports. Absent owner reply is not permission. Re-run after owner overlay is available, extending strict base-source guard only with explicit owner-approved source hash manifest; never silently accept drift. Original Rule.lean still requires exact-file owner coordination if a future fix is needed.

Final exports: `/workspace/migrate-stipend-evidence/original.patch`, `migration.bundle`, `HANDOFF.md`, `SHA256SUMS`, `result.json`. The post-commit HANDOFF/result record full committed head and checksum paths. Bulk compiler outputs/toolchains stay off git. No final toolchain edit belongs to this lane.


## 2026-11-07 resumed baseline and API tooling (partial)

The coordinator explicitly requested rebaseline/continuation after merge. Fetched
origin/master at `5da4771e63a4278ed53932ac39a032e3d7aea6ed` and fast-forwarded
this same lane, preserving retirement ancestry/artifacts. No new/replacement
goal or push. All 12 closure sources still match the original frozen base;
Stipend.Rule is unchanged. The known unchanged Raw failure was not rerun.
Original benchmarks remain historical; no new timing delta or Lean execution.

public_api.py fixture deterministically generates the isolated
`tests/h62/item6/migrate-stipend/PublicInventory.lean`. It enumerates ModuleData
kernel/compiler-extra names with no generated/private/internal exclusion,
records raw types, ordered universes/telescope binders, axiom names and naming
flags, and retains missing signatures as unresolved. The exporter is NOT
compiled/validated and has produced no actual inventory. Naming flags do not
establish export visibility/accessibility; raw equality is not semantic
equivalence. Added declarations require separate trust audit; no shim exists.

CLI extract/compare requires saved successful-run receipts bound to log/source/
fixture/object bytes, exact pinned versions/archive fields, old4.24/new4.35
roles and unambiguous serial command metadata. This is consistency checking,
not execution attestation or H81 approval. Current source binding refuses
changed-source snapshots until explicit approved provenance is added. Full
migration gate status remains false.

22 external controls pass: completeness/counts/duplicates, generated/private
names, unresolved types, universe/binder changes, new axioms, failed/mismatched
receipts, exact versions, role pairing, conflicting threads, input hashes,
exclusive evidence preservation and fixture reproduction. Independent finder
and skeptic found/rechecked the receipt/version/role/thread fixes; neither ran
Lean/server. Their reviews and exact open state are committed under
`tests/h62/item6/migrate-stipend/resume-20261107/`.

Registration/root and fragment checks pass. The broader layer gate FAILS on
the unchanged baseline: 901 core modules, 12 new core-to-non-core edges (95
pinned allowances). Full diagnostics: `/workspace/migrate-stipend-resume-20261107/layers.log`.
Production and checker sources match the resume baseline; this is an upstream
wait, not a passing final gate. No outside-scope source change was made.

Evidence: `/workspace/migrate-stipend-resume-20261107/`. Q-RESUME-H81 requested
current VM-readable resource policy before new Lean work. Raw migration,
resource review, real generated API/visibility evidence, exporter/Stipend
compilation, new fixtures, affected/final gates, matched timings and future
milestone reviews remain open. No RUNTIME_GATE_PASS or queue completion claim.
