# H62 item 6 migrate-hash: applied overlay, full gate blocked

Repository `/workspace/migrate-hash`, branch `codex/solidity-h62-6-20261106/migrate-hash`,
pinned base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
`origin/master` was fetched and base ancestry verified. The older clean `work`
checkout at `/workspace/solidity-lean` was preserved. This branch was created at
exactly the base; no push, merge, PR, cut-over or live-producer ownership transfer.
The exported result records the full committed head after this document's commit.

| Checkpoint | State | Evidence / remaining work |
|---|---|---|
| 1. Pinned census and clean old build | partial | Source census and directory baseline pass; complete public/generated API inventory and full old baseline remain pending |
| 2. Identical new toolchain and adaptation | partial | Official pin and applied proof patch pass named checks; H78 complete public generated exports and shim assessment remain pending |
| 3. New build and performance | blocked | Production Hash passes; clean full gate fails outside Hash in Syntax.Raw; old full baseline and matched comparison pending |
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
Pinned original whole-source hashes (production proof bodies are now migrated):

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
Coordinator resolved Q-HASH-RSS: per-module time/memory growth does not stop this
lane. Record these numbers and continue to the matched clean full-build comparison;
the coordinator reports growth to the human with cut-over escalation. The module
numbers do not establish a full-build comparison. No final runtime-pass claim.

## Cross-directory handoff

Direct external importers: `Solidity/Storage/HashedLayout.lean`,
`Solidity/Roadmap/Contracts.lean`, `Bridge/SolidityBridge/HashBridge/Queries.lean`,
and the generated root. They remain read-only. There are no incoming dependencies
outside Hash. Root migration must validate these consumers and their transitive
affected closures using the identical toolchain. No new production module exists,
so the registration fragment is empty; generated roots, central maps and axiom
pins are unchanged. Bridge validation remains an external/optional dependency gate.

Coordinator resolved Q-HASH-OWNER: relay.sh exists only on the coordinator host;
the isolated migration lane is the registered writer of Hash. The exact tested
patch is applied to both production Hash files. The coordinator will relay the
following changes to the live owner at cut-over:

- `CollisionBound`: explicit contains-cons simplification in `countP_contains_le`;
  explicit proposition extraction in `countP_near_le` and `countP_covers_le`;
  deprecated proof lemma aliases replaced by current `ite_*` names.
- `Adaptive`: direct zero-query proofs in `two_mul_eagerCollides_le` and
  `two_mul_eagerRegionsFail_le`; deprecated proof lemma aliases replaced.
- No declaration type, definition body, premise, exclusion, axiom guard, or proof
  budget changes. No producer ownership change. Kernel `decide +kernel` controls
  are expressly allowed by coordinator H64 steering. Tracked lean-toolchain stays
  at 4.24; the final global toolchain edit belongs to migration root.

Production acceptance in `new-production-acceptance-1` passes KeySort, both Hash
files, 121 named API checks, 97 theorem axiom audits, four instances and 19 controls
through actual production imports. Inputs are hash-bound and unchanged.

The corrected full-repository probe `full_measure.py ... --migrated` at
`/workspace/migrate-hash-full/new-full-4` uses a clean pinned detached worktree,
only the Hash overlay, a private toolchain override, and the unchanged original
`run-lean.sh` as its final gate. It schedules 6,389 modules in validated topological
order, builds both `+module:o` and `+module:o.noexport` serially, then links the two executables serially, and keeps the
same 12 GiB address-space cap/4 GiB available reserve/no-swap budget. Every module has
a 300s timeout; the final aggregate gate separately has an 1800s timeout. Both arms
use identical private package configuration (SHA256
e7519519bf936dcd920c5b6577fda1136391d79227ca92746aae30fae5a9585f)
and fresh disabled caches. No outside-owner source is patched.

**Owner migration request REQ-HASH-SYNTAX-RAW:** the full new probe exits 1 after
4 / 6389 successful modules at Solidity.Syntax.Raw. Five String API errors occur at
597:44, 650:23, 665:27, 684:34 and 682:46: String.drop now returns String.Slice, slice
toList and String.dropRight are unavailable, and endsWith has a changed inferred
function type. Exact errors are in the copied `full-new-probe` evidence and
`coordination.json`. Source hashes remain unchanged, and no resource stop occurs.
This is an out-of-scope owner migration dependency, not a performance verdict.

The original old full attempt was interrupted for the independent review's native
object serialization correction; its `aborted.json` excludes it from performance
claims. The corrected clean old baseline at
`/workspace/migrate-hash-full/old-full-2` terminated at its existing native command
cap after 18 / 6389 modules. Inspect `baseline-controller.json` and the preserved
summary before any future baseline disposition; no controller is actively running.
No complete clean full-build baseline is available.


Pending: owner overlays for Syntax.Raw and any further full-graph migration errors,
completed old baseline, matched successful clean full-build comparison, full affected
importer/runtime validation, and migrate-root-gate receipt. No snapshot or failed
full probe replaces those gates. Both earlier questions are resolved; no scope
question is pending.

In-scope backfill completed: declaration census, negative scanner controls, isolated
fixture proofs, all-declaration API/axiom checks, semantic controls and deterministic
measurement/export tooling. No newly unclaimed cleanup scope was taken.

## Independent read-only reviews

Finder and skeptic ran independently, without Lean/server calls or edits. Both
confirmed actual frozen statements, definition bodies and proof budgets unchanged.
Findings fixed: guaranteed kill/reap on timeout/resource exceptions; fail-closed
scanner handling of modifiers/indentation/standalone attributes; definition-body
hashes; explicit four-instance checks; source-bound logs including Inventory and
Controls; and per-module growth reporting. Later coordinator steering makes
per-module growth nonblocking; matched full-build escalation belongs to root gate. Final reviews
approve the production patch and corrected serial native-object driver, explicitly
retaining the out-of-scope Syntax.Raw and full-gate blockers. Full review record is `/workspace/migrate-hash-evidence/reviews.md`.

## Gates and retrieval

Native old/new builds: exit 0 in their `results.json`; prerequisite KeySort passes.
Final production per-file API/axiom/control acceptance: `new-production-acceptance-1/results.json`, all five
commands exit 0 with empty proof/control error logs. Source-bound audit:
`python3 scripts/h62/item6/migrate-hash/acceptance.py /workspace/migrate-hash-evidence`,
exit 0, `acceptance-after-application.log`. Static layer check passes (857 core modules; zero
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

## H70 consolidated producer delivery

The coordinator routed twenty-three consumers of CollisionBound. The reviewed production
repair is exported as `/workspace/migrate-hash-evidence/hash-owner-overlay.patch`
(two files) and `collision-bound-overlay.patch` (CollisionBound only). Exact base,
committed head, before/after file hashes, patch hashes, all twenty-three requester IDs,
validation boundaries and live-owner changes are in `producer-overlay.json`. These
are ready for coordinator retrieval/approved consumption; no direct cross-VM write,
push, merge, ownership transfer or full-gate claim is made. The source census at the
pinned base and all frozen axiom-message guards remain intact.

## H70 routed continuation: supervisor inspected, no restart

The corrected old supervisor has terminated. PID 36556 is a zombie, not an active
controller; no active Lean/compiler job remains. Its saved summary records 18 of
6389 modules passed, unchanged inputs and MODULE_TIMEOUT during the 300-second
combined native command for Solidity.Calculus.RuleSyntax.Grammar. The Lean log
reports that module elaborated in 36s; native object compilation remained pending.
No restart, budget change, source change or new Lean run was performed during this
continuation. Prior supervisor/worktree/output files are preserved. Terminal
metadata and logs are copied to `full-old-baseline` in the evidence package.
This incomplete prefix cannot establish clean full-build timing or RSS; in
particular, killed-wrapper RSS does not represent completed descendant/group RSS.
REQ-HASH-BASELINE-NATIVE-TIMEOUT records the root-gate disposition request.

The Hash migration source remains exactly the reviewed commit
2a18afcdba00a85645b0b3079704f78ffcd78860; this continuation changes only receipts
and handoff tooling/documentation. Both producer patch SHA256 values and both
production file hashes remain unchanged. Newly routed recipients audit-roadmap,
statement-graph, migrate-roadmap and vy2-physical are included in the expanded
sixteen-consumer delivery record. Other staged requester payloads were neither
applied nor reviewed; only their explicit Hash prerequisite requests are recorded.
The coordinator has staged/routed the reviewed overlay. Wait for migrate-syntax's
Raw.lean overlay and root-gate baseline disposition before full comparison.

## H70 exact source-commit provenance reply

Root-gate at ac7d4535b16c9a393a2b86ec91dd44fae2f418f2 requested static provenance
only for the previously reviewed source head 2a18afcdba00a85645b0b3079704f78ffcd78860.
The immutable package `/workspace/migrate-hash-evidence/source-provenance-2a18afcdb`
contains the exact source-head bundle, full base-to-source diff, scoped Hash patch,
raw commit object, before/after Git blob IDs and SHA256 file hashes, plus snapshots
of retained production results/settings/versions/logs and reviews. `manifest.json`
is SHA256 23e366c6e73ab79a4a32e9739db4dae58ff8aadfe69854b6353b54a1edfe1a9a;
`source.bundle` is SHA256 a17167daff48fbe5a74b33d95676a66130c88ed92f4309329fc3ca801a60cabc.
The source bundle advertises exactly 2a18 as HEAD and requires the pinned base.
Static checks validate ancestry, raw commit object identity, exact bundle ref and
patch digest, file/blob hashes and equality of current production source to 2a18.
No source application or Lean rerun occurs. Root acceptance remains unclaimed.

The delivery catalog now includes twenty-three unique consumers, adding the new
H55/g49, p16-generator, language/lowering/semantics/solcvalidation and root-gate
requests without taking any work or ownership from those lanes. The coordinator
reports generic-primitive-packets checked both Hash modules in isolated staged
sources and cleared that prerequisite; its separate Roadmap.Contracts trust guard
remains an owner blocker. That peer result is recorded as reported, not replayed.
All current STOPs, trust requirements and budgets are retained. The old supervisor
and its outputs remain untouched; no baseline restart. Full assignment remains
blocked on Syntax.Raw, old-baseline disposition, matched full comparison and final
affected/root gates.

## H82 final retirement: supersedes all implementation continuation text

Human-approved stop-and-handoff retires this worker to successor
solidity-h62-6-20261106/migrate-root-gate. No new proof work, Lean run, baseline
restart, budget change or source application. The successor is responsible for
integrating the final committed head after the final stopped/head acknowledgement.
This worker must not auto-resume. Existing goal PAUSED is authorized, but no exposed
goal tool supports PAUSED; only complete/blocked are available. No substitute
transition and no goal completion/reset/creation is performed. Precise pause
capability failure is in retirement/pause-report.json.

The full first task user turn from this original thread, original queue/backfill,
original goal/environment and exact scope manifest are committed under
tests/h62/item6/migrate-hash/retirement/. The task text's own checksum is recorded;
it does not reproduce the separately advertised rendered-prompt digest ad33d9e4.
No original renderer/envelope was found. Preserve that provenance limitation.

All open work, backfill and schema-v1 waits are in retirement/successor-state.json
and waits.json. H78 includes all original public generated declarations; existing
121 named APIs/97 theorem audits do not establish that coverage. Exact old/new
exports and shim records remain pending. No shims are guessed or implemented.
The original four checkpoints remain incomplete overall, notwithstanding the
reviewed Hash proof patch and retained passing directory checks.

No H71 branch-push permission text was supplied to this VM/session, so the original
no-push rule is retained. Local cumulative patch, Git bundle and authenticated
artifact handoff are exported to /workspace/migrate-hash-h82-handoff. The original
VM/branch/worktrees/toolchains/bulk evidence remain intact. No master push/merge.
Coordinator-local source paths are provenance only; actual copied mandatory input
files are included in the handoff. Future successor checks require current H81
policy and applicable trust/performance/public-API dispositions.

## Explicit post-retirement limited pre-gate repair

The coordinator explicitly requested fixing this lane's failed pre-gate, first
merging origin/master706e36825929 and then pushing only the original lane branch.
This is a limited repair authorization; it does not resume the retired full queue
or waive prior H78, trust, performance, baseline or final-gate obligations.

Merged exact master706e36825929d6d0084dc08b88de9349abcd25aa as merge commit
86b259fdce240c1beb8f9d4e721d375d2e47a3e5. Master still pins Lean4.24.0; its core
does not define ite_eq_left/ite_eq_right. Replace those proof-only references in
both Hash files with if_pos/if_neg, available in4.24 and4.35. Keep the explicit
contains-cons/proposition-extraction/zero-query proof repairs and every original
statement, definition, import, axiom-message guard and resource/proof budget. The
fixture generator now retains these compatible names instead of restoring the
new-only names. Lean4.35 emits expected alias-deprecation warnings, with no errors.

The updated repository per-file gate checks KeySort, CollisionBound and Adaptive
on each official toolchain. Both runs exit0, source hashes remain unchanged, and
no resource stop occurs. Each uses fresh separate build/cache paths, package -j1,
LEAN_NUM_THREADS=1, an8GiB address-space cap, no configured swap,4GiB effective
available-memory reserve and300s total command timeout.4.24:14.9024s,425528KiB
max child RSS;4.35:9.4475s,595580KiB. These validation runs are not a matched clean
full-build performance comparison. Logs, exact commands/settings/source hashes and
independent read-only finder/skeptic results are saved off git under
/workspace/migrate-hash-repair-706e36825929. No Lean MCP tools are exposed, so the
repository's gate.sh per-file fallback was used. The source census confirms125
original declarations, identical signature/context/definition hashes and no budget
change. Full affected gate.sh touched remains for the coordinator's next pre-gate;
no local full runtime or original-assignment completion claim.

No master push, default-branch merge, source-scope expansion, new goal or old
baseline restart. Only the explicit current instruction authorizes the lane push;
original retirement artifacts remain unchanged as historical handoffs. After the
repair handoff this worker returns to the H82 stopped state.
